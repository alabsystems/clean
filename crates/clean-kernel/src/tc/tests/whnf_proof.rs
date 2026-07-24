// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for proof-producing WHNF reduction (whnf_proof module).
//!
//! Tests cover all reduction kinds: beta, delta, zeta, iota, proj, transparent (MData/Squash), and multi-step.
//! Each type-checking test verifies generated proof terms via `infer_type`.
//!
//! Part of #685.

use std::sync::Arc;

use super::*;
use crate::env::Declaration;
use crate::expr::BinderInfo;
use crate::tc::whnf_proof::{CongrArgArgs, EqProofBuilder, WhnfProofStep};

fn assert_app_head(e: &Expr, expected: &str) {
    if let ExprKind::Const(name, _) = &e.get_app_fn().kind {
        assert_eq!(name.to_string(), expected);
    } else {
        panic!("expected Const {expected}, got {:?}", e.get_app_fn().kind);
    }
}

fn env_with_eq() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("invariant: init_nat");
    env.init_eq().expect("invariant: init_eq");
    env
}

/// Assert proof term has type `@Eq.{u1} type_ lhs rhs`.
fn assert_eq_proof(tc: &TypeChecker, proof: &Expr, type_: Expr, lhs: Expr, rhs: Expr) {
    let ty = tc.infer_type(proof).expect("proof must type-check");
    let u1 = Level::succ(Level::zero());
    let expected = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![u1]),
        [type_, lhs, rhs],
    );
    assert!(tc.is_def_eq(&ty, &expected), "proof type mismatch: {ty:?}");
}

/// Build a Nat.rec identity application: `Nat.rec motive zero_case succ_case target`
/// where motive = λ _ => Nat, zero_case = Nat.zero, succ_case = λ n ih => Nat.succ ih.
fn build_nat_rec_id(target: Expr) -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    let zero_case = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat,
            Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                Expr::bvar(0),
            ),
        ),
    );
    let nat_rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    Expr::apps(nat_rec, [motive, zero_case, succ_case, target])
}

#[test]
fn test_eq_proof_builder_structure() {
    let u = Level::succ(Level::zero());
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let refl = EqProofBuilder::mk_eq_refl(u.clone(), nat.clone(), zero);
    assert_app_head(&refl, "Eq.refl");
    assert_eq!(refl.get_app_args().len(), 2);
    let (a, b, c) = (
        Expr::const_str("a"),
        Expr::const_str("b"),
        Expr::const_str("c"),
    );
    let trans = EqProofBuilder::mk_eq_trans(
        u,
        nat,
        a,
        b,
        c,
        Expr::const_str("hab"),
        Expr::const_str("hbc"),
    );
    assert_app_head(&trans, "Eq.trans");
    assert_eq!(trans.get_app_args().len(), 6);
}

#[test]
fn test_chain_proofs() {
    let u = Level::succ(Level::zero());
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let hab = Expr::const_(Name::from_string("hab"), vec![]);
    let single = EqProofBuilder::chain_proofs(
        u.clone(),
        nat.clone(),
        a.clone(),
        vec![(Expr::const_str("b"), hab.clone())],
    );
    assert_eq!(single, hab);
    let two = EqProofBuilder::chain_proofs(
        u,
        nat,
        a,
        vec![
            (Expr::const_str("b"), hab),
            (Expr::const_str("c"), Expr::const_str("hbc")),
        ],
    );
    assert_app_head(&two, "Eq.trans");
}

#[test]
fn test_whnf_with_proof_beta_and_no_reduction() {
    let mut env = Environment::new();
    env.init_nat().expect("invariant: init_nat");
    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Beta: (fun x : Nat => x) Nat.zero  ~>  Nat.zero
    let id_fn = Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0));
    let app = Expr::app(id_fn, zero.clone());
    let result = tc.whnf_with_proof(&app, &nat, Level::succ(Level::zero()));
    assert_eq!(result.result, zero);
    assert!(result.proof.is_some());
    assert!(matches!(result.steps[0], WhnfProofStep::Beta));

    // No reduction: Nat.zero stays Nat.zero
    let result = tc.whnf_with_proof(&zero, &nat, Level::succ(Level::zero()));
    assert_eq!(result.result, zero);
    assert!(result.proof.is_none());
    assert!(result.steps.is_empty());
}

#[test]
fn test_whnf_with_proof_head_reduces_no_beta() {
    // When the function head reduces via delta but the result is NOT a
    // lambda and iota/quot don't apply, we must still record a proof step.
    let mut env = Environment::new();
    env.init_nat().expect("invariant: init_nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let my_id_name = Name::from_string("myId");
    let my_id_type = Expr::pi(BinderInfo::Default, nat.clone(), nat.clone());
    env.add_decl(Declaration::Definition {
        name: my_id_name.clone(),
        level_params: vec![],
        type_: my_id_type,
        value: nat_succ.clone(),
        is_reducible: true,
    })
    .expect("invariant: add_decl");
    let tc = TypeChecker::new(&env);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let app = Expr::app(Expr::const_(my_id_name, vec![]), zero.clone());
    let result = tc.whnf_with_proof(&app, &nat, Level::succ(Level::zero()));
    let expected = Expr::app(nat_succ, zero);
    assert_eq!(result.result, expected);
    assert!(result.proof.is_some(), "head reduction needs proof");
    assert!(!result.steps.is_empty(), "head reduction needs steps");
}

#[test]
fn test_beta_proof_typechecks() {
    let env = env_with_eq();
    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let app = Expr::app(
        Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0)),
        zero.clone(),
    );
    let wp = tc.whnf_with_proof(&app, &nat, Level::succ(Level::zero()));
    assert_eq!(wp.result, zero);
    assert_eq_proof(&tc, &wp.proof.expect("beta needs proof"), nat, app, zero);
}

#[test]
fn test_delta_proof_typechecks() {
    let mut env = env_with_eq();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    env.add_decl(Declaration::Definition {
        name: Name::from_string("myZero"),
        level_params: vec![],
        type_: nat.clone(),
        value: zero.clone(),
        is_reducible: true,
    })
    .expect("invariant: add_decl");
    let tc = TypeChecker::new(&env);
    let my_zero = Expr::const_(Name::from_string("myZero"), vec![]);
    let wp = tc.whnf_with_proof(&my_zero, &nat, Level::succ(Level::zero()));
    assert_eq!(wp.result, zero);
    assert!(matches!(wp.steps[0], WhnfProofStep::Delta(_)));
    assert_eq_proof(
        &tc,
        &wp.proof.expect("delta needs proof"),
        nat,
        my_zero,
        zero,
    );
}

#[test]
fn test_zeta_proof_typechecks() {
    let env = env_with_eq();
    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let let_expr = Expr::let_named(
        Name::anon(),
        nat.clone(),
        zero.clone(),
        Expr::bvar(0),
        false,
    );
    let wp = tc.whnf_with_proof(&let_expr, &nat, Level::succ(Level::zero()));
    assert_eq!(wp.result, zero);
    assert!(matches!(wp.steps[0], WhnfProofStep::Zeta));
    assert_eq_proof(
        &tc,
        &wp.proof.expect("zeta needs proof"),
        nat,
        let_expr,
        zero,
    );
}

#[test]
fn test_multi_step_proof_typechecks() {
    let mut env = env_with_eq();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    env.add_decl(Declaration::Definition {
        name: Name::from_string("myZero"),
        level_params: vec![],
        type_: nat.clone(),
        value: zero.clone(),
        is_reducible: true,
    })
    .expect("invariant: add_decl");
    let tc = TypeChecker::new(&env);
    let app = Expr::app(
        Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0)),
        Expr::const_(Name::from_string("myZero"), vec![]),
    );
    let wp = tc.whnf_with_proof(&app, &nat, Level::succ(Level::zero()));
    assert_eq!(wp.result, zero);
    assert!(wp.steps.len() >= 2, "expected beta + delta steps");
    assert_eq_proof(
        &tc,
        &wp.proof.expect("multi-step needs proof"),
        nat,
        app,
        zero,
    );
}

#[test]
fn test_iota_zero_proof_typechecks() {
    // Nat.rec (λ _ => Nat) Nat.zero (λ n ih => succ ih) Nat.zero  ~>  Nat.zero
    let env = env_with_eq();
    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let app = build_nat_rec_id(zero.clone());

    let wp = tc.whnf_with_proof(&app, &nat, Level::succ(Level::zero()));
    assert_eq!(
        wp.result, zero,
        "Nat.rec on zero should reduce to zero_case"
    );
    assert!(
        wp.steps.iter().any(|s| matches!(s, WhnfProofStep::Iota)),
        "should have iota step",
    );
    assert_eq_proof(&tc, &wp.proof.expect("iota needs proof"), nat, app, zero);
}

#[test]
fn test_iota_succ_proof_typechecks() {
    // Nat.rec (λ _ => Nat) Nat.zero (λ n ih => succ ih) (succ zero)
    //   ~> (λ n ih => succ ih) zero (Nat.rec ... zero)   [iota]
    //   ~> succ (Nat.rec ... zero)                        [beta]
    // WHNF stops here (argument is not reduced further).
    let env = env_with_eq();
    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_zero = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        zero.clone(),
    );
    let app = build_nat_rec_id(succ_zero);

    let wp = tc.whnf_with_proof(&app, &nat, Level::succ(Level::zero()));
    // Result is Nat.succ (Nat.rec ... Nat.zero) -- head is constructor, WHNF stops.
    assert!(
        matches!(wp.result.kind, ExprKind::App(ref f, _) if matches!(f.kind, ExprKind::Const(ref n, _) if n.to_string() == "Nat.succ")),
        "result head should be Nat.succ, got {:?}",
        wp.result.kind,
    );
    assert!(
        wp.steps.iter().any(|s| matches!(s, WhnfProofStep::Iota)),
        "should have iota step",
    );
    assert!(
        wp.steps.len() >= 2,
        "expected iota + beta steps, got {}",
        wp.steps.len()
    );
    assert_eq_proof(
        &tc,
        &wp.proof.expect("iota+beta needs proof"),
        nat,
        app,
        wp.result.clone(),
    );
}

#[test]
fn test_mdata_stripping_produces_proof() {
    // MData(_, Nat.zero) should reduce to Nat.zero with a proof step
    let env = env_with_eq();
    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let mdata_zero = Expr::mdata(vec![], zero.clone());

    let wp = tc.whnf_with_proof(&mdata_zero, &nat, Level::succ(Level::zero()));
    assert_eq!(wp.result, zero, "MData wrapping should be stripped");
    // The key assertion: a proof MUST be produced when the result differs
    assert!(
        wp.proof.is_some(),
        "MData stripping changes the expr, so a proof step must be recorded"
    );
    assert!(
        matches!(wp.steps[0], WhnfProofStep::Transparent),
        "MData stripping should use Transparent step, got {:?}",
        wp.steps[0]
    );
    assert_eq_proof(
        &tc,
        &wp.proof.expect("MData stripping needs proof"),
        nat,
        mdata_zero,
        zero,
    );
}

#[test]
fn test_mdata_with_inner_reduction_proof_typechecks() {
    // MData(_, (fun x : Nat => x) Nat.zero)  ~>  Nat.zero with proof
    let env = env_with_eq();
    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let id_fn = Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0));
    let beta_app = Expr::app(id_fn, zero.clone());
    let mdata_beta = Expr::mdata(vec![], beta_app);

    let wp = tc.whnf_with_proof(&mdata_beta, &nat, Level::succ(Level::zero()));
    assert_eq!(wp.result, zero, "MData + beta should reduce to zero");
    assert!(wp.proof.is_some(), "multi-step reduction needs proof");
    // Proof should cover the full path: MData(_, (λ x, x) 0) ~> 0
    assert_eq_proof(
        &tc,
        &wp.proof.expect("MData+beta needs proof"),
        nat,
        mdata_beta,
        zero,
    );
}

/// Squash is NOT transparent in WHNF — it is a type former, not metadata.
/// whnf_with_proof should return the Squash expression unchanged. See #2164.
#[test]
fn test_squash_not_stripped_by_whnf_proof() {
    let env = env_with_eq();
    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let squash_zero = Expr::from_kind(ExprKind::Squash(Arc::new(zero)));

    let wp = tc.whnf_with_proof(&squash_zero, &nat, Level::succ(Level::zero()));
    assert_eq!(
        wp.result, squash_zero,
        "Squash should NOT be stripped by WHNF"
    );
    assert!(
        wp.proof.is_none(),
        "No reduction occurred, so no proof step should be recorded"
    );
    assert!(wp.steps.is_empty(), "No reduction steps for opaque Squash");
}

#[test]
fn test_eq_proof_builder_congr_fun_structure() {
    let u = Level::succ(Level::zero());
    let v = Level::succ(Level::zero());
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let proof = EqProofBuilder::mk_congr_fun(
        u,
        v,
        nat.clone(),
        nat,
        Expr::const_str("f"),
        Expr::const_str("g"),
        Expr::const_str("h"),
        Expr::const_str("a"),
    );
    // congrFun' α β f g h a → 6 args
    assert_app_head(&proof, "congrFun'");
    assert_eq!(proof.get_app_args().len(), 6);
}

#[test]
fn test_eq_proof_builder_congr_structure() {
    let u = Level::succ(Level::zero());
    let v = Level::succ(Level::zero());
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let proof = EqProofBuilder::mk_congr(
        u,
        v,
        nat.clone(),
        nat,
        Expr::const_str("f1"),
        Expr::const_str("f2"),
        Expr::const_str("a1"),
        Expr::const_str("a2"),
        Expr::const_str("hf"),
        Expr::const_str("ha"),
    );
    // congr α β f₁ f₂ a₁ a₂ hf ha → 8 args
    assert_app_head(&proof, "congr");
    assert_eq!(proof.get_app_args().len(), 8);
}

#[test]
fn test_eq_proof_builder_eq_subst_structure() {
    let u = Level::succ(Level::zero());
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let proof = EqProofBuilder::mk_eq_subst(
        u,
        nat,
        Expr::const_str("motive"),
        Expr::const_str("a"),
        Expr::const_str("b"),
        Expr::const_str("h"),
        Expr::const_str("m"),
    );
    // Eq.subst α motive a b h m → 6 args
    assert_app_head(&proof, "Eq.subst");
    assert_eq!(proof.get_app_args().len(), 6);
}

#[test]
fn test_eq_proof_builder_congr_arg_via_struct() {
    let u = Level::succ(Level::zero());
    let v = Level::succ(Level::zero());
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let proof = EqProofBuilder::mk_congr_arg(CongrArgArgs {
        u,
        v,
        alpha: nat.clone(),
        beta: nat,
        a1: Expr::const_str("a1"),
        a2: Expr::const_str("a2"),
        f: Expr::const_str("f"),
        h: Expr::const_str("h"),
    });
    // congrArg α β a₁ a₂ f h → 6 args
    assert_app_head(&proof, "congrArg");
    assert_eq!(proof.get_app_args().len(), 6);
}
