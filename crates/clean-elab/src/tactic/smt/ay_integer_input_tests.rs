// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exercise integer preparation through the actual AY target/hypothesis caller.

use super::ay_solver::create_smt_backend;
use super::ay_tactics::{
    assert_goal_hypotheses_with_drop_count, register_goal_fvars, run_ay_tactic,
};
use super::ay_types::{AyConfig, SmtVerifyPolicy};
use super::bridge_reconstruction::{try_bridge_reconstruction_candidate, BridgeProbeOutcome};
use super::prepare_integer_ops::prepare_smt_integer_expr;
use super::prepare_integer_ops_tests::source_state;
use crate::tactic::{Goal, LocalDecl, ProofState};
use clean_auto::bridge::ay_contract::AyLogic;
use clean_kernel::{Expr, FVarId, Name};
use clean_parser::SurfaceName;

fn strict_config() -> AyConfig {
    AyConfig::default().with_verify_policy(SmtVerifyPolicy::VerifyStrict)
}

fn assert_registered_source_proof(state: &ProofState, goal: &Goal) {
    assert!(state.is_complete());
    let mut proof = state
        .instantiated_proof()
        .expect("closed source goal proof");
    state
        .check_type_strict(goal, &proof, &goal.target)
        .expect("strict kernel checks against the original source target");
    let mut ty = goal.target.clone();
    for local in goal.local_ctx.iter().rev() {
        assert!(
            local.value.is_none(),
            "these source fixtures have ordinary parameters"
        );
        proof = Expr::lam(
            clean_kernel::BinderInfo::Default,
            local.ty.clone(),
            proof.abstract_fvar(local.fvar),
        );
        ty = Expr::pi(
            clean_kernel::BinderInfo::Default,
            local.ty.clone(),
            ty.abstract_fvar(local.fvar),
        );
    }
    let mut env = state.env().clone();
    let name = Name::from_string("smtIntegerSourceProof");
    env.add_decl(clean_kernel::env::Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: ty,
        value: proof,
    })
    .expect("register the real closed theorem through the strict kernel");
    let info = env.get_const(&name).expect("registered source theorem");
    let tc = clean_kernel::TypeChecker::new(&env);
    let inferred = tc
        .infer_type_full(info.value.as_ref().expect("real theorem proof value"))
        .expect("strictly re-infer the registered proof");
    assert!(tc.is_def_eq(&inferred, &info.type_));
    assert!(env
        .axiom_deps(&name)
        .expect("whole theorem axiom closure")
        .is_empty());
    assert_eq!(state.trust_ledger().trusted_ay_count, 0);
}

#[test]
fn test_ay_caller_integer_projection_target_keeps_original_kernel_goal() {
    for source in [
        "def smtInput (a b : Int) : Prop := a / b = a / b",
        "def smtInput : Prop := (7 : Int) / (3 : Int) = (2 : Int)",
        "def smtInput : Prop := (Int.negSucc 6) / (Int.ofNat 2) = (Int.negSucc 3)",
    ] {
        let mut state = source_state(source);
        let goal = state.current_goal().expect("source goal").clone();
        run_ay_tactic(
            &mut state,
            &strict_config(),
            AyLogic::QfLia,
            "integer_source",
        )
        .unwrap_or_else(|error| {
            panic!("real AY caller without outer decide fallback: {source}: {error}")
        });
        assert_registered_source_proof(&state, &goal);
    }
}

#[test]
fn test_ay_caller_uses_the_original_integer_hypothesis_proof_in_both_policies() {
    let source = source_state("def smtInput (a b : Int) : Prop := a / b = Int.ofNat 2");
    let source_goal = source.current_goal().expect("source proposition");
    let mut context = source_goal.local_ctx.clone();
    context.push(LocalDecl {
        binder_info: Default::default(),
        fvar: FVarId::new(2),
        name: SurfaceName::component("h", false),
        ty: source_goal.target.clone(),
        value: None,
    });
    for policy in [SmtVerifyPolicy::TrustSolver, SmtVerifyPolicy::VerifyStrict] {
        let mut state = ProofState::with_context(
            source.env().clone(),
            source_goal.target.clone(),
            context.clone(),
        );
        let goal = state
            .current_goal()
            .expect("original hypothesis goal")
            .clone();
        run_ay_tactic(
            &mut state,
            &AyConfig::default().with_verify_policy(policy),
            AyLogic::QfLia,
            "integer_hypothesis_use",
        )
        .unwrap_or_else(|error| {
            panic!("{policy:?} must use the actual source hypothesis: {error}")
        });
        assert_registered_source_proof(&state, &goal);
    }
}

#[test]
fn test_ay_caller_refuses_false_integer_quotient_and_custom_dictionary_targets() {
    for policy in [SmtVerifyPolicy::TrustSolver, SmtVerifyPolicy::VerifyStrict] {
        for source in [
            "def smtInput : Prop := (Int.negSucc 6) / (Int.ofNat 2) = (Int.negSucc 2)",
            "def smtInput (a b : Int) : Prop := \
         @HDiv.hDiv Int Int Int (@HDiv.mk Int Int Int (fun x y => x)) a b = a",
            "def «Int.ofNat» (n : Nat) : Int := Int.ofNat 0\n\
             def smtInput : Prop := «Int.ofNat» 7 = Int.ofNat 7",
        ] {
            let mut state = source_state(source);
            assert!(
                run_ay_tactic(
                    &mut state,
                    &AyConfig::default().with_verify_policy(policy),
                    AyLogic::QfLia,
                    "integer_negative"
                )
                .is_err(),
                "{source}"
            );
            assert!(!state.is_complete());
            assert!(state.instantiated_proof().is_none());
        }
    }
}

#[test]
fn test_ay_integer_source_transport_signs_zero_modulus_and_large_numerals_in_both_policies() {
    for (body, expected) in [
        ("(Int.negSucc 6) / (Int.ofNat 2) = (Int.negSucc 3)", true),
        ("(Int.negSucc 6) / (Int.ofNat 2) = (Int.negSucc 2)", false),
        ("(Int.negSucc 6) / (Int.negSucc 1) = (Int.ofNat 4)", true),
        ("(Int.negSucc 6) / (Int.ofNat 0) = (Int.ofNat 0)", true),
        ("(Int.negSucc 6) % (Int.ofNat 2) = (Int.ofNat 1)", true),
        ("(Int.negSucc 6) % (Int.ofNat 0) = (Int.negSucc 6)", true),
        (
            "(18446744073709551616 : Int) / (2 : Int) = (9223372036854775808 : Int)",
            true,
        ),
    ] {
        let state = source_state(&format!("def smtInput : Prop := {body}"));
        let goal = state.current_goal().expect("source arithmetic proposition");
        let prepared = prepare_smt_integer_expr(&state, goal, &goal.target)
            .expect("checked integer preparation");
        for policy in [SmtVerifyPolicy::TrustSolver, SmtVerifyPolicy::VerifyStrict] {
            let config = AyConfig::default().with_verify_policy(policy);
            let mut backend = create_smt_backend(&config, AyLogic::QfLia);
            let outcome = backend
                .prove(&prepared)
                .expect("real solver handles typed source arithmetic");
            assert_eq!(outcome.proved, expected, "{policy:?}: {body}");
        }
    }
}

#[test]
fn test_kernel_computation_recovery_refuses_a_false_quotient() {
    let mut state =
        source_state("def smtInput : Prop := (Int.negSucc 6) / (Int.ofNat 2) = (Int.negSucc 2)");
    let goal = state.current_goal().expect("false source goal").clone();
    let prepared =
        prepare_smt_integer_expr(&state, &goal, &goal.target).expect("typed preparation");
    assert!(!matches!(
        try_bridge_reconstruction_candidate(&mut state, &goal, &prepared, "false_computation"),
        BridgeProbeOutcome::Candidate(_)
    ));
    assert!(!state.is_complete());
}

#[test]
fn test_kernel_reflexivity_candidate_retains_embedded_trusted_subterm_debt() {
    let mut env = clean_kernel::Environment::with_prelude();
    env.init_trusted_ay()
        .expect("existing test-only trust marker");
    let truth = Expr::const_(Name::from_string("True"), vec![]);
    let marker = Expr::app(
        Expr::const_(
            Name::from_string("trustedAy"),
            vec![clean_kernel::Level::zero()],
        ),
        truth.clone(),
    );
    let target = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![clean_kernel::Level::zero()]),
        [truth, marker.clone(), marker],
    );
    let mut state = ProofState::new(env, target);
    let goal = state
        .current_goal()
        .expect("trust-marker equality goal")
        .clone();
    let BridgeProbeOutcome::Candidate(candidate) =
        try_bridge_reconstruction_candidate(&mut state, &goal, &goal.target, "trusted_reflexivity")
    else {
        panic!("kernel reflexivity can construct a candidate without accepting its trust debt");
    };
    state
        .check_type_strict(&goal, &candidate.proof, &goal.target)
        .expect("candidate is strictly typed");
    assert_eq!(candidate.trust_subterm_count, 1);
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "probing does not select the candidate"
    );
    assert!(!state.is_complete());
}

#[test]
fn test_ay_caller_keeps_exists_witnesses_fresh_against_skipped_proof_locals() {
    let source = source_state("def smtInput : Prop := ∃ x : Int, x = x");
    let exists = source
        .current_goal()
        .expect("source existential")
        .target
        .clone();
    let truth = Expr::const_(Name::from_string("True"), vec![]);
    let state = ProofState::with_context(
        source.env().clone(),
        truth.clone(),
        vec![
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(0),
                name: SurfaceName::component("h", false),
                ty: truth,
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(1),
                name: SurfaceName::component("hx", false),
                ty: exists,
                value: None,
            },
        ],
    );
    let goal = state.current_goal().expect("source context goal");
    let mut backend = create_smt_backend(&strict_config(), AyLogic::QfLia);
    register_goal_fvars(&state, goal, &mut backend, "exists_freshness")
        .expect("register typed source context");
    assert_eq!(
        assert_goal_hypotheses_with_drop_count(&state, goal, &mut backend),
        0
    );
    let bindings = backend.exists_witness_bindings();
    assert_eq!(bindings.len(), 1);
    let witness = &bindings[0];
    assert_eq!(witness.source_hyp_fvar, FVarId::new(1));
    assert_ne!(witness.witness_fvar, witness.witness_proof_fvar);
    for local in &goal.local_ctx {
        assert_ne!(witness.witness_fvar, local.fvar);
        assert_ne!(witness.witness_proof_fvar, local.fvar);
    }
}

#[test]
fn test_ay_caller_integer_hypothesis_preparation_retains_checked_proof_mapping() {
    for (source, expected_drops) in [
        ("def smtInput : Prop := (7 : Int) / (3 : Int) = (2 : Int)", 0),
        ("def smtInput : Prop := \
          @HDiv.hDiv Int Int Int (@HDiv.mk Int Int Int (fun x y => x)) (Int.ofNat 7) (Int.ofNat 3) = Int.ofNat 7", 1),
    ] {
        let source = source_state(source);
        let hypothesis = source.current_goal().expect("source proposition").target.clone();
        let fvar = FVarId::new(20);
        let state = ProofState::with_context(
            source.env().clone(), Expr::const_(Name::from_string("True"), vec![]),
            vec![LocalDecl { binder_info: Default::default(), fvar, name: SurfaceName::component("h", false), ty: hypothesis.clone(), value: None }],
        );
        let goal = state.current_goal().expect("hypothesis goal");
        assert!(state.infer_type_strict(goal, &hypothesis).expect("strict source hypothesis check").is_prop());
        let mut backend = create_smt_backend(&strict_config(), AyLogic::QfLia);
        register_goal_fvars(&state, goal, &mut backend, "integer_hypothesis").expect("register actual typed context");
        assert_eq!(assert_goal_hypotheses_with_drop_count(&state, goal, &mut backend), expected_drops);
        if expected_drops == 0 {
            let mapped = backend.registered_hypothesis("fvar_20").expect("asserted proof variable remains registered");
            assert_eq!(mapped.0, fvar);
            assert_eq!(mapped.1, Expr::fvar(fvar));
            assert!(state.is_def_eq(goal, &hypothesis, &mapped.2));
        } else {
            assert!(backend.registered_hypothesis("fvar_20").is_none());
        }
    }
}
