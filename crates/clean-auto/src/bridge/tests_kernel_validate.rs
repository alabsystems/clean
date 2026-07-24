// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel type-checking tests for proof reconstruction.
//!
//! These tests use a full init_eq() environment and validate that proof terms
//! produced by SmtBridge are well-typed according to the kernel TypeChecker.
//! This catches ill-typed proof terms that structural tests (ProofStep checks)
//! miss.

use super::tests::make_eq;
use super::*;
use crate::proof::ProofStep;
use clean_kernel::env::Declaration;
use clean_kernel::{BinderInfo, Level, LocalContext};

/// Create an environment with proper Eq inductive (all eliminators)
/// plus test constants A, a, b, c, d, e : A and f : A → A.
fn setup_env_with_eq() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq should succeed");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    for name in ["a", "b", "c", "d", "e"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("A"), vec![]),
        })
        .unwrap();
    }

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::arrow(
            Expr::const_(Name::from_string("A"), vec![]),
            Expr::const_(Name::from_string("A"), vec![]),
        ),
    })
    .unwrap();

    env
}

pub(super) fn setup_env_with_eq_exists() -> Environment {
    let mut env = setup_env_with_eq();
    env.init_exists().expect("init_exists should succeed");
    env
}

pub(super) fn make_exists(ty: Expr, body: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Exists"),
                vec![Level::succ(Level::zero())],
            ),
            ty.clone(),
        ),
        Expr::lam(BinderInfo::Default, ty, body),
    )
}

/// Kernel-validate a proof term: verify TypeChecker::infer_type succeeds
/// and the inferred type is definitionally equal to the expected goal type.
pub(super) fn kernel_validate_proof(
    env: &Environment,
    proof: &Expr,
    expected_type: &Expr,
    hyp_fvars: &[(FVarId, Expr)],
) {
    use clean_kernel::tc::LocalContext;

    let mut ctx = LocalContext::new();
    for (fvar_id, ty) in hyp_fvars {
        let assigned_id = ctx.push(
            Name::from_string(&format!("h{}", fvar_id.as_u64())),
            ty.clone(),
            BinderInfo::Default,
        );
        assert_eq!(
            assigned_id, *fvar_id,
            "LocalContext assigned FVarId {assigned_id:?} but bridge used {fvar_id:?}. \
             Adjust hyp_fvar IDs to match LocalContext sequential allocation."
        );
    }

    let tc = TypeChecker::with_context(env, ctx);
    let inferred = tc.infer_type(proof).unwrap_or_else(|e| {
        panic!(
            "Proof term failed kernel type inference: {e:?}\nProof: {proof:?}\nExpected type: {expected_type:?}"
        )
    });

    assert!(
        tc.is_def_eq(&inferred, expected_type),
        "Inferred type does not match expected goal type.\nInferred: {inferred:?}\nExpected: {expected_type:?}"
    );
}

/// Test that a symmetry proof term (b = a from h : a = b) is kernel-valid.
#[test]
fn test_proof_kernel_validates_symmetry() {
    let env = setup_env_with_eq();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // FVarId(0) matches LocalContext::push() first allocation
    let hyp_fvar = FVarId::new(0);
    let hyp_type = make_eq(a_ty.clone(), a.clone(), b.clone());
    bridge
        .add_hypothesis_with_fvar(&hyp_type, Some(hyp_fvar))
        .unwrap();

    let goal = make_eq(a_ty, b, a);
    let result = bridge
        .prove(&goal)
        .unwrap()
        .verified()
        .expect("Should prove b = a");
    let proof = result.proof_term();

    kernel_validate_proof(&env, proof, &goal, &[(hyp_fvar, hyp_type)]);
}

/// Test that a transitivity proof term (a = c from h1 : a = b, h2 : b = c)
/// is kernel-valid.
#[test]
fn test_proof_kernel_validates_transitivity() {
    let env = setup_env_with_eq();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    let h1_fvar = FVarId::new(0);
    let h2_fvar = FVarId::new(1);
    let h1_type = make_eq(a_ty.clone(), a.clone(), b.clone());
    let h2_type = make_eq(a_ty.clone(), b.clone(), c.clone());
    bridge
        .add_hypothesis_with_fvar(&h1_type, Some(h1_fvar))
        .unwrap();
    bridge
        .add_hypothesis_with_fvar(&h2_type, Some(h2_fvar))
        .unwrap();

    let goal = make_eq(a_ty, a, c);
    let result = bridge
        .prove(&goal)
        .unwrap()
        .verified()
        .expect("Should prove a = c");
    let proof = result.proof_term();

    kernel_validate_proof(
        &env,
        proof,
        &goal,
        &[(h1_fvar, h1_type), (h2_fvar, h2_type)],
    );
}

/// Test that a 4-step transitive chain proof term is kernel-valid.
/// a = b, b = c, c = d, d = e → a = e
#[test]
fn test_proof_kernel_validates_long_chain() {
    let env = setup_env_with_eq();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let d = Expr::const_(Name::from_string("d"), vec![]);
    let e = Expr::const_(Name::from_string("e"), vec![]);

    let fvars: Vec<FVarId> = (0..4).map(FVarId::new).collect();
    let hyps = vec![
        make_eq(a_ty.clone(), a.clone(), b.clone()),
        make_eq(a_ty.clone(), b.clone(), c.clone()),
        make_eq(a_ty.clone(), c.clone(), d.clone()),
        make_eq(a_ty.clone(), d.clone(), e.clone()),
    ];

    for (fvar, hyp) in fvars.iter().zip(hyps.iter()) {
        bridge.add_hypothesis_with_fvar(hyp, Some(*fvar)).unwrap();
    }

    let goal = make_eq(a_ty, a, e);
    let result = bridge
        .prove(&goal)
        .unwrap()
        .verified()
        .expect("Should prove a = e");
    let proof = result.proof_term();

    let hyp_pairs: Vec<_> = fvars.into_iter().zip(hyps).collect();
    kernel_validate_proof(&env, proof, &goal, &hyp_pairs);
}

/// Test that the mixed-direction Eq.trans path added in #2442 still checks
/// against the real kernel `Eq.symm`/`Eq.trans` declarations, not just the
/// bridge-local test axioms.
#[test]
fn test_build_propositional_proof_kernel_validates_mixed_direction_chain() {
    let env = setup_env_with_eq();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let d = Expr::const_(Name::from_string("d"), vec![]);

    let h_ab_fvar = FVarId::new(0);
    let h_cb_fvar = FVarId::new(1);
    let h_cd_fvar = FVarId::new(2);
    let h_ab_type = make_eq(a_ty.clone(), a.clone(), b.clone());
    let h_cb_type = make_eq(a_ty.clone(), c.clone(), b.clone());
    let h_cd_type = make_eq(a_ty.clone(), c.clone(), d.clone());

    bridge
        .add_hypothesis_with_fvar(&h_ab_type, Some(h_ab_fvar))
        .unwrap();
    bridge
        .add_hypothesis_with_fvar(&h_cb_type, Some(h_cb_fvar))
        .unwrap();
    bridge
        .add_hypothesis_with_fvar(&h_cd_type, Some(h_cd_fvar))
        .unwrap();

    let goal = make_eq(a_ty, a, d);
    let goal_class = bridge.classify_prop(&goal);
    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("mixed-direction chain should reconstruct via Eq.trans");

    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Eq.trans"));
    kernel_validate_proof(
        &env,
        &proof,
        &goal,
        &[
            (h_ab_fvar, h_ab_type),
            (h_cb_fvar, h_cb_type),
            (h_cd_fvar, h_cd_type),
        ],
    );
}

/// Test that a congruence proof term (f(a) = f(b) from h : a = b) is kernel-valid.
/// This is the key acceptance criterion for #2103: congruence proofs must
/// produce well-typed kernel terms without falling back to trustedAy.
#[test]
fn test_proof_kernel_validates_congruence() {
    let env = setup_env_with_eq();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let fa = Expr::app(f.clone(), a.clone());
    let fb = Expr::app(f, b.clone());

    let hyp_fvar = FVarId::new(0);
    let hyp_type = make_eq(a_ty.clone(), a, b);
    bridge
        .add_hypothesis_with_fvar(&hyp_type, Some(hyp_fvar))
        .unwrap();

    let goal = make_eq(a_ty, fa, fb);
    let result = bridge
        .prove(&goal)
        .unwrap()
        .verified()
        .expect("Should prove f(a) = f(b)");
    let proof = result.proof_term();

    // Verify the proof head is congrArg (not a fallback like trustedAy)
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string().contains("congr")),
        "Proof should use congrArg, not a fallback. Got head: {head:?}"
    );

    kernel_validate_proof(&env, proof, &goal, &[(hyp_fvar, hyp_type)]);
}

/// Test that a nested congruence proof (f(f(a)) = f(f(b)) from h : a = b) is
/// kernel-valid.
#[test]
fn test_proof_kernel_validates_nested_congruence() {
    let env = setup_env_with_eq();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let ffa = Expr::app(f.clone(), Expr::app(f.clone(), a.clone()));
    let ffb = Expr::app(f.clone(), Expr::app(f, b.clone()));

    let hyp_fvar = FVarId::new(0);
    let hyp_type = make_eq(a_ty.clone(), a, b);
    bridge
        .add_hypothesis_with_fvar(&hyp_type, Some(hyp_fvar))
        .unwrap();

    let goal = make_eq(a_ty, ffa, ffb);
    let result = bridge
        .prove(&goal)
        .unwrap()
        .verified()
        .expect("Should prove f(f(a)) = f(f(b))");
    let proof = result.proof_term();

    kernel_validate_proof(&env, proof, &goal, &[(hyp_fvar, hyp_type)]);
}

/// Test that a multi-argument congruence proof (g(a,c) = g(b,d) from
/// h1 : a = b, h2 : c = d) is kernel-valid. Exercises the congr path
/// (not just congrArg) in ProofBuilder::mk_congr_multi.
#[test]
fn test_proof_kernel_validates_multi_arg_congruence() {
    let mut env = setup_env_with_eq();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    // g : A → A → A (2-ary function, extends setup_env_with_eq's A, a, b, c, d)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("g"),
        level_params: vec![],
        type_: Expr::arrow(a_ty.clone(), Expr::arrow(a_ty.clone(), a_ty.clone())),
    })
    .unwrap();

    let mut bridge = SmtBridge::new(&env);

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let d = Expr::const_(Name::from_string("d"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);

    let gac = Expr::app(Expr::app(g.clone(), a.clone()), c.clone());
    let gbd = Expr::app(Expr::app(g, b.clone()), d.clone());

    let h1_fvar = FVarId::new(0);
    let h2_fvar = FVarId::new(1);
    let h1_type = make_eq(a_ty.clone(), a, b);
    let h2_type = make_eq(a_ty.clone(), c, d);
    bridge
        .add_hypothesis_with_fvar(&h1_type, Some(h1_fvar))
        .unwrap();
    bridge
        .add_hypothesis_with_fvar(&h2_type, Some(h2_fvar))
        .unwrap();

    let goal = make_eq(a_ty, gac, gbd);
    let result = bridge
        .prove(&goal)
        .unwrap()
        .verified()
        .expect("Should prove g(a,c) = g(b,d)");
    let proof = result.proof_term();

    kernel_validate_proof(
        &env,
        proof,
        &goal,
        &[(h1_fvar, h1_type), (h2_fvar, h2_type)],
    );
}

#[test]
fn test_instantiate_body_unmapped_witness_returns_none() {
    // Regression test for #2084: unmapped witness terms must return None,
    // not fabricate synthetic FVarIds with magic offsets.
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let body = Expr::bvar(0);
    let bound_vars = vec![0u32];
    // TermId(9999) is not in term_to_expr — must return None
    let witness_terms = vec![TermId(9999)];

    let result = bridge.instantiate_body_with_terms(&body, &bound_vars, &witness_terms);
    assert!(
        result.is_none(),
        "Unmapped witness term must return None, not a fabricated FVarId"
    );
}

#[test]
fn test_proof_kernel_validates_exists_with_constant_witness() {
    let env = setup_env_with_eq_exists();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let goal = make_exists(a_ty.clone(), make_eq(a_ty, Expr::bvar(0), a.clone()));

    let result = bridge
        .prove(&goal)
        .unwrap()
        .verified()
        .expect("Should prove ∃ x : A, x = a");
    let proof = result.proof_term();

    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string() == "Exists.intro"),
        "Proof should use Exists.intro, got {head:?}"
    );
    kernel_validate_proof(&env, proof, &goal, &[]);
}

#[test]
fn test_proof_kernel_validates_exists_with_local_witness() {
    let env = setup_env_with_eq_exists();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let witness_fvar = FVarId::new(0);
    let witness = Expr::fvar(witness_fvar);
    let goal = make_exists(a_ty.clone(), make_eq(a_ty.clone(), Expr::bvar(0), witness));

    let mut local_ctx = LocalContext::new();
    let assigned = local_ctx.push(Name::from_string("x"), a_ty.clone(), BinderInfo::Default);
    assert_eq!(
        assigned, witness_fvar,
        "expected sequential local FVar allocation"
    );

    bridge.set_local_ctx(local_ctx);

    let result = bridge
        .prove(&goal)
        .unwrap()
        .verified()
        .expect("Should prove ∃ y : A, y = x");
    let proof = result.proof_term();

    kernel_validate_proof(&env, proof, &goal, &[(witness_fvar, a_ty)]);
}
